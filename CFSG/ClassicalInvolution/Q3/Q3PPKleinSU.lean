module

public import CFSG.ClassicalInvolution.Q3.Q3PPKleinModels
public import CFSG.ClassicalInvolution.Q3.Q3URTransfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups

section Transfer

theorem KleinData.of_equiv {c c' : CompData} (e : c.G ≃* c'.G)
    (he : ∀ R : Subgroup c.G, R ∈ c.fund ↔ R.map e.toMonoidHom ∈ c'.fund) (h : KleinData c') :
    KleinData c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_center_iff] at hz
    have hz' : e z ∈ Subgroup.center c'.G := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hz w]
    rw [h.center, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (e.injective (by rw [hz', map_one]))
  · intro R hR a ha b hb ha2 hb2 ha1 hb1
    have := h.unique_inv (R.map e.toMonoidHom) ((he R).mp hR) (e a) ⟨a, ha, rfl⟩ (e b)
      ⟨b, hb, rfl⟩ (by rw [← map_mul, ha2, map_one]) (by rw [← map_mul, hb2, map_one])
      (fun h1 => ha1 (e.injective (by rw [h1, map_one])))
      (fun h1 => hb1 (e.injective (by rw [h1, map_one])))
    exact e.injective this
  · intro R hR g
    have h1 := h.conj_fund (R.map e.toMonoidHom) ((he R).mp hR) (e g)
    have hmap : (conjSub g R).map e.toMonoidHom = conjSub (e g) (R.map e.toMonoidHom) := by
      ext x
      simp only [Subgroup.mem_map, mem_conjSub_iff, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g⁻¹ * y * g, hy, by simp⟩
      · rintro ⟨s, hs, hsx⟩
        refine ⟨g * s * g⁻¹, ?_, ?_⟩
        · simpa [mul_assoc] using hs
        · have : x = e g * e s * (e g)⁻¹ := by rw [hsx]; group
          rw [this]
          simp
    exact (he _).mpr (hmap ▸ h1)
  · intro R hR r hrR hr2 hr1
    obtain ⟨r', g', g'', h1, h2, h3, h4⟩ := h.klein (R.map e.toMonoidHom) ((he R).mp hR) (e r)
      ⟨r, hrR, rfl⟩ (by rw [← map_mul, hr2, map_one])
      (fun h1 => hr1 (e.injective (by rw [h1, map_one])))
    refine ⟨e.symm r', e.symm g', e.symm g'', ?_, ?_, ?_, ?_⟩
    · apply e.injective
      simpa [map_mul] using h1
    · apply e.injective
      rw [map_mul]
      simpa [map_mul] using h2
    · apply e.injective
      simpa [map_mul] using h3
    · intro h5
      apply h4
      have := congrArg e h5
      simpa using this

end Transfer

section SU3

theorem center_su_three_eq_bot :
    Subgroup.center (Phan.Su (GaloisField 3 2) 3 1 3) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_center_iff] at hA
  have h2 : (2 : GaloisField 3 2) ≠ 0 := two_ne_zero_gf9
  set M := Models.suMat A with hM
  have hcomm : ∀ T : Models.Pair 3, Models.zMat (GaloisField 3 2) 3 T.1 * M =
      M * Models.zMat (GaloisField 3 2) 3 T.1 := by
    intro T
    have := congrArg Models.suMat (hA (Models.zEltU (GaloisField 3 2) 3 1 T))
    simpa [Models.suMat_mul, Models.suMat_zEltU] using this
  have key : ∀ T : Models.Pair 3, ∀ i j : Fin 3, ¬ (i ∈ T.1 ↔ j ∈ T.1) → M i j = 0 := by
    intro T i j hT
    have h := congrFun (congrFun (hcomm T) i) j
    simp only [Models.zMat, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    by_cases hi : i ∈ T.1 <;> by_cases hj : j ∈ T.1
    · exact absurd (iff_of_true hi hj) hT
    · simp only [hi, hj, ite_true, ite_false] at h
      have h' : (2 : GaloisField 3 2) * M i j = 0 := by
        linear_combination (-1 : GaloisField 3 2) * h
      exact (mul_eq_zero.mp h').resolve_left h2
    · simp only [hi, hj, ite_true, ite_false] at h
      have h' : (2 : GaloisField 3 2) * M i j = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    · exact absurd (iff_of_false hi hj) hT
  have hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact key ⟨{0, 1}, by decide⟩ _ _ (by decide)
        | exact key ⟨{0, 2}, by decide⟩ _ _ (by decide)
  have hdiagM : M = Matrix.diagonal (fun a => M a a) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hoff i j hij
  set τ : Equiv.Perm (Fin 3) := finRotate 3 with hτ
  set Q := Models.monoSU (GaloisField 3 2) 3 1 (by norm_num : 0 < 3) τ with hQdef
  have hQm : Models.monoMat (GaloisField 3 2) τ * M = M * Models.monoMat (GaloisField 3 2) τ := by
    have := congrArg Models.suMat (hA Q)
    simpa [Models.suMat_mul, hQdef, Models.suMat_monoSU] using this
  have hmono := Models.isMonomialFor_monoMat (K := GaloisField 3 2) τ
  have hEq : Matrix.diagonal (fun a => M a a) * Models.monoMat (GaloisField 3 2) τ =
      Matrix.diagonal (fun b => M (τ.symm b) (τ.symm b)) * Models.monoMat (GaloisField 3 2) τ := by
    calc Matrix.diagonal (fun a => M a a) * Models.monoMat (GaloisField 3 2) τ
        = Models.monoMat (GaloisField 3 2) τ * Matrix.diagonal (fun a => M a a) := by
          rw [← hdiagM]
          exact hQm.symm
      _ = Matrix.diagonal (fun b => M (τ.symm b) (τ.symm b)) *
            Models.monoMat (GaloisField 3 2) τ := hmono.mul_diagonal _
  have hinv : Models.monoMat (GaloisField 3 2) τ * Models.suMat Q⁻¹ = 1 := by
    have := Models.suMat_mul_suMat_inv Q
    rwa [hQdef, Models.suMat_monoSU] at this
  have hdd : Matrix.diagonal (fun a => M a a) =
      Matrix.diagonal (fun b => M (τ.symm b) (τ.symm b)) := by
    have := congrArg (· * Models.suMat Q⁻¹) hEq
    simpa [Matrix.mul_assoc, hinv] using this
  have hd : ∀ a, M a a = M (τ.symm a) (τ.symm a) := fun a => by
    have := congrFun (congrFun hdd a) a
    simpa using this
  have h10 : M 1 1 = M 0 0 := by
    have := hd 1
    have e1 : τ.symm 1 = 0 := by decide
    rwa [e1] at this
  have h21 : M 2 2 = M 1 1 := by
    have := hd 2
    have e1 : τ.symm 2 = 1 := by decide
    rwa [e1] at this
  have hscal : M = Matrix.diagonal (fun _ => M 0 0) := by
    rw [hdiagM]
    congr 1
    funext a
    fin_cases a
    · rfl
    · exact h10
    · exact h21.trans h10
  have hdet : (M 0 0) ^ 3 = 1 := by
    have h1 := Models.det_suMat A
    rw [← hM, hscal, Matrix.det_diagonal] at h1
    simpa using h1
  have hc : M 0 0 = 1 := by
    have h3 : (M 0 0 - 1) ^ 3 = 0 := by
      rw [sub_pow_char (p := 3), hdet, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h3)
  rw [Subgroup.mem_bot]
  apply Models.suMat_injective
  rw [← hM, hscal, hc, Models.suMat_one]
  exact Matrix.diagonal_one

@[expose] noncomputable def compSU3 : CompData :=
  ⟨Phan.Su (GaloisField 3 2) 3 1 3,
    Models.longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) (by norm_num : 2 ≤ 3)⟩

theorem kleinData_compSU3 : KleinData compSU3 := by
  have hn : 2 ≤ 3 := by norm_num
  have h2 : (2 : GaloisField 3 2) ≠ 0 := two_ne_zero_gf9
  let T₀ : Models.Pair 3 :=
    ⟨{⟨0, by omega⟩, ⟨0 + 1, by omega⟩}, Finset.card_pair (by simp)⟩
  let T₁ : Models.Pair 3 :=
    ⟨{⟨0, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  let T₂ : Models.Pair 3 :=
    ⟨{⟨1, by omega⟩, ⟨2, by omega⟩}, Finset.card_pair (by simp [Fin.ext_iff])⟩
  have hroot : Models.rootInvSU (GaloisField 3 2) 3 1 hn =
      Models.zEltU (GaloisField 3 2) 3 1 T₀ := by
    apply Models.suMat_injective
    rw [Models.suMat_rootInvSU, Models.suMat_zEltU,
      Models.negBlock_eq_zMat (by omega : 0 + 2 ≤ 3)]
  have hfund : ∀ R : Subgroup (Phan.Su (GaloisField 3 2) 3 1 3), R ∈ compSU3.fund ↔
      ∃ g, R = conjSub g (Models.rootSU2 (GaloisField 3 2) 3 1 hn) :=
    fun R => Models.mem_longRootSetU_iff hn
  have hstd := Models.isLongRootSU2_standard (K := GaloisField 3 2) (p := 3) (f := 1) hn
  have hprod' : Models.zEltU (GaloisField 3 2) 3 1 T₀ * Models.zEltU (GaloisField 3 2) 3 1 T₁ =
      Models.zEltU (GaloisField 3 2) 3 1 T₂ := by
    apply Models.suMat_injective
    rw [Models.suMat_mul, Models.suMat_zEltU, Models.suMat_zEltU, Models.suMat_zEltU]
    simp only [Models.zMat, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    fin_cases a <;> simp [T₀, T₁, T₂]
  refine KleinData.of_conjClass (R₀ := Models.rootSU2 (GaloisField 3 2) 3 1 hn)
    (ρ := Models.rootInvSU (GaloisField 3 2) 3 1 hn)
    (ρ₁ := Models.zEltU (GaloisField 3 2) 3 1 T₁) (ρ₂ := Models.zEltU (GaloisField 3 2) 3 1 T₂)
    hfund center_su_three_eq_bot ?_ ?_ ?_ ?_ ?_ ?_
  · have huniq : ∀ b : Phan.Su (GaloisField 3 2) 3 1 3,
        b ∈ Models.rootSU2 (GaloisField 3 2) 3 1 hn → b * b = 1 → b ≠ 1 →
          b = Models.rootInvSU (GaloisField 3 2) 3 1 hn := by
      intro b hb hb2 hb1
      exact hstd.eq_of_orderOf_eq_two card_gf9 (by norm_num) hb
        (orderOf_eq_prime (by rwa [pow_two]) hb1)
    intro a ha ha2 ha1
    exact huniq a ha ha2 ha1
  · obtain ⟨g, -, hg⟩ := Models.isLongRootSU2_LcU (K := GaloisField 3 2) (p := 3) (f := 1) h2 hn T₁
    exact ⟨g, hg⟩
  · obtain ⟨g, -, hg⟩ := Models.isLongRootSU2_LcU (K := GaloisField 3 2) (p := 3) (f := 1) h2 hn T₂
    exact ⟨g, hg⟩
  · rw [hroot]
    exact Models.signGroupU_comm (Models.zEltU_mem_signGroupU T₁) (Models.zEltU_mem_signGroupU T₀)
  · rw [hroot]
    exact hprod'
  · rw [hroot]
    intro h
    have h01 : T₁.1 = T₀.1 := Models.zMat_inj h2 (congrArg Models.suMat h)
    exact absurd h01 (by decide)

theorem kleinData_psu_three (hadm : StatedLieAdmissible .PSU 3 3 1) :
    KleinData (CompData.model .PSU 3) := by
  obtain ⟨e, he⟩ := psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
  exact KleinData.of_equiv (c' := compSU3) e (fun R => he R) kleinData_compSU3

end SU3

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

theorem EdgeData.kleinAt_of_psu_three (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hk : D.kind i = CompData.model .PSU 3) (hadm : StatedLieAdmissible .PSU 3 3 1) :
    KleinAt K K₁ z₂ :=
  h.kleinAt_of_kleinData hR D hi (by rw [hk]; exact kleinData_psu_three hadm)

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
