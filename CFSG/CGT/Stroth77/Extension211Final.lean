module

public import CFSG.CGT.Stroth77.Extension211

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem rho_gens_t211 (m : ℕ) (hm : 2 ≤ m) :
    (StrothTypeIndex.t211 m hm).action.φρ (gen (StrothTypeIndex.t211 m hm).k 0) =
        gen (StrothTypeIndex.t211 m hm).k 0 ∧
    (StrothTypeIndex.t211 m hm).action.φρ (gen (StrothTypeIndex.t211 m hm).k 1) =
        gen (StrothTypeIndex.t211 m hm).k 2 ∧
    (StrothTypeIndex.t211 m hm).action.φρ (gen (StrothTypeIndex.t211 m hm).k 2) =
      (-1 : ℤ) • gen (StrothTypeIndex.t211 m hm).k 0 +
        (-1 : ℤ) • gen (StrothTypeIndex.t211 m hm).k 1 +
        (-1 : ℤ) • gen (StrothTypeIndex.t211 m hm).k 2 := by
  have hc := Type211.rho_c m hm
  have ha := Type211.rho_a m hm
  have hb := Type211.rho_b m hm
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  refine ⟨?_, ?_, ?_⟩
  · change (Type211.action m hm).φρ (gen (Type211.k m) 0) = gen (Type211.k m) 0
    rw [hc]
    module
  · change (Type211.action m hm).φρ (gen (Type211.k m) 1) = gen (Type211.k m) 2
    rw [ha]
    module
  · exact hb

theorem hk_t211 (m : ℕ) (hm : 2 ≤ m) : ∀ i, 1 ≤ (StrothTypeIndex.t211 m hm).k i := by
  intro i
  fin_cases i <;> simp [StrothTypeIndex.k, Type211.k] <;> omega

theorem exists_basis_t211_of_data {m : ℕ} {hm : 2 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t211 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, ∃ hdC : d ∈ C, d ∉ B ∧ d * d = (D.c : S) ∧
      ∃ E : Torus (Type120.k (m + 1)) ≃+ Additive C,
        E (gen _ 0) = Additive.ofMul ⟨d, hdC⟩ ∧
        E (gen _ 1) = Additive.ofMul ⟨D.a, hBC D.a.2⟩ ∧
        E (gen _ 2) = Additive.ofMul ⟨D.b, hBC D.b.2⟩ := by
  obtain ⟨hρ0, hρ1, hρ2⟩ := rho_gens_t211 m hm
  obtain ⟨d, hdC, hdB, hd2⟩ := exists_sq_eq_c_Idx2R D (-1) (hk_t211 m hm) hρ0 hρ1 hρ2
    hBC hC hrel (hL D.ρ_mem_L) hH hcS hne
  obtain ⟨E, hE0, hE1, hE2⟩ := exists_torusEquiv_Idx2R D (k' := Type120.k (m + 1))
    rfl rfl rfl hBC hC hrel hdC hdB hd2
  exact ⟨d, hdC, hdB, hd2, E, hE0, hE1, hE2⟩

theorem exists_basis_t211 {m : ℕ} {hm : 2 ≤ m}
    (hB : HasStrothType B (StrothTypeIndex.t211 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, ∃ hdC : d ∈ C, d ∉ B ∧ d * d = (hB.data.c : S) ∧
      ∃ E : Torus (Type120.k (m + 1)) ≃+ Additive C,
        E (gen _ 0) = Additive.ofMul ⟨d, hdC⟩ ∧
        E (gen _ 1) = Additive.ofMul ⟨hB.data.a, hBC hB.data.a.2⟩ ∧
        E (gen _ 2) = Additive.ofMul ⟨hB.data.b, hBC hB.data.b.2⟩ :=
  exists_basis_t211_of_data hB.data hBC hC hrel hL hH hcS hne

theorem eq_two_of_noInvolutionsCentralizing_t211_of_data {m : ℕ} {hm : 2 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t211 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) : m = 2 := by
  obtain ⟨d, hdC, -, hd2, E, hE0, hE1, hE2⟩ := exists_basis_t211_of_data D hBC hC hrel hL hH hcS hne
  have TU := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.u_mem_L) D.u_mem _ _
    D.u_conj
  have hUU := DFunLike.congr_fun (conjTorusIdx4_rels E D hL).u_sq (gen (Type120.k (m + 1)) 0)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hUU
  obtain ⟨s, rfl⟩ : ∃ s, m = s + 2 := ⟨m - 2, by omega⟩
  have hM : ∀ i j, (StrothTypeIndex.t211 (s + 2) hm).action.u i j = Type211.uM (s + 2) i j :=
    fun _ _ => rfl
  refine eq_two_of_u_Idx2R (k' := Type120.k (s + 2 + 1)) (m := s + 2) (n := s + 2 + 2) rfl rfl
    rfl hm (by omega) _ hUU (2 * 2 ^ s) (-(2 * 2 ^ s) * (2 * 2 ^ s + 1)) ?_ ?_ ?_
  · rw [TU.1]
    congr 1
    funext i
    fin_cases i <;> simp [hM, Type211.uM, uMat, ofCols_apply, pow_add]
    ring
  · rw [TU.2.1]
    congr 1
  · rw [TU.2.2]
    congr 1
    funext i
    fin_cases i <;> simp [hM, Type211.uM, uMat, ofCols_apply]

theorem eq_two_of_noInvolutionsCentralizing_t211 {m : ℕ} {hm : 2 ≤ m}
    (hB : HasStrothType B (StrothTypeIndex.t211 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) : m = 2 :=
  eq_two_of_noInvolutionsCentralizing_t211_of_data hB.data hBC hC hrel hL hH hcS hne

theorem images_t120_three :
    (StrothTypeIndex.t120 3 le_rfl).action.φuv (gen (StrothTypeIndex.t120 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![-171, 2, -2] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φt (gen (StrothTypeIndex.t120 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![-167, 2, 4] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φu (gen (StrothTypeIndex.t120 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![-1, 0, 0] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φρ (gen (StrothTypeIndex.t120 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![1, 0, 0] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φuv (gen (StrothTypeIndex.t120 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![29070, -855, 342] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φt (gen (StrothTypeIndex.t120 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![12996, -1197, -1368] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φu (gen (StrothTypeIndex.t120 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![-340, 0, 1] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φρ (gen (StrothTypeIndex.t120 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![0, 0, 1] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φuv (gen (StrothTypeIndex.t120 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![-8011350, -876546, 88065] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φt (gen (StrothTypeIndex.t120 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![28386, -342, -1197] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φu (gen (StrothTypeIndex.t120 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![-340, 1, 0] ∧
    (StrothTypeIndex.t120 3 le_rfl).action.φρ (gen (StrothTypeIndex.t120 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![-2, -1, -1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (matAct_gen_ofInt_Idx2R _ _ _).trans (by congr 1 <;> decide)

theorem images_t130_three :
    (StrothTypeIndex.t130 3 le_rfl).action.φuv (gen (StrothTypeIndex.t130 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![-171, 10, -2] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φt (gen (StrothTypeIndex.t130 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![-167, 2, 12] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φu (gen (StrothTypeIndex.t130 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![3, 0, 0] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φρ (gen (StrothTypeIndex.t130 3 le_rfl).k 0) =
        Torus.ofInt (Type120.k 3) ![1, 0, 0] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φuv (gen (StrothTypeIndex.t130 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![29070, -855, 342] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φt (gen (StrothTypeIndex.t130 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![12996, -1197, -1368] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φu (gen (StrothTypeIndex.t130 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![-340, 0, 1] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φρ (gen (StrothTypeIndex.t130 3 le_rfl).k 1) =
        Torus.ofInt (Type120.k 3) ![0, 0, 1] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φuv (gen (StrothTypeIndex.t130 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![-8476470, -1109106, -144495] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φt (gen (StrothTypeIndex.t130 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![28386, -342, -1197] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φu (gen (StrothTypeIndex.t130 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![1020, 1, 0] ∧
    (StrothTypeIndex.t130 3 le_rfl).action.φρ (gen (StrothTypeIndex.t130 3 le_rfl).k 2) =
        Torus.ofInt (Type120.k 3) ![-2, -1, -1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (matAct_gen_ofInt_Idx2R _ _ _).trans (by congr 1 <;> decide)

theorem hasStrothType_t120_or_t130_of_noInvolutionsCentralizing_t211 {m : ℕ} {hm : 2 ≤ m}
    (hB : HasStrothType B (StrothTypeIndex.t211 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothType C (StrothTypeIndex.t120 (m + 1) (by omega)) ∨
    HasStrothType C (StrothTypeIndex.t130 (m + 1) (by omega)) := by
  have hm2 := eq_two_of_noInvolutionsCentralizing_t211 hB hBC hC hrel hL hH hcS hne
  subst hm2
  obtain ⟨d, hdC, -, hd2, E, hE0, hE1, hE2⟩ := exists_basis_t211 hB hBC hC hrel hL hH hcS hne
  let D := hB.data
  have TV := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.uv_mem_L) D.uv_mem _ _
    D.uv_conj
  have TW := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.t_mem_L) D.t_mem _ _
    D.t_conj
  have TU := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.u_mem_L) D.u_mem _ _
    D.u_conj
  have TR := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.ρ_mem_L) D.ρ_mem _ _
    D.ρ_conj
  obtain ⟨zv, hz, hz0, h⟩ := classify_t211 _ _ _ _ (conjTorusIdx4_rels E D hL)
    (by rw [TV.1]; congr 1 <;> decide +revert) (by rw [TV.2.1]; congr 1 <;> decide +revert)
    (by rw [TV.2.2]; congr 1 <;> decide +revert)
    (by rw [TW.1]; congr 1 <;> decide +revert) (by rw [TW.2.1]; congr 1 <;> decide +revert)
    (by rw [TW.2.2]; congr 1 <;> decide +revert)
    (by rw [TU.1]; congr 1 <;> decide +revert) (by rw [TU.2.1]; congr 1 <;> decide +revert)
    (by rw [TU.2.2]; congr 1 <;> decide +revert)
    (by rw [TR.1]; congr 1 <;> decide +revert) (by rw [TR.2.1]; congr 1 <;> decide +revert)
    (by rw [TR.2.2]; congr 1 <;> decide +revert)
  let E' : Torus (Type120.k 3) ≃+ Additive C := (shearIdx2R _ hk0_t211 zv hz hz0).trans E
  have hE' : ∀ {g : S} (hg : g ∈ Subgroup.normalizer C) (x : Torus (Type120.k 3)),
      conjTorusIdx4 E' hg x =
        shearHomIdx2R _ hk0_t211 zv hz (conjTorusIdx4 E hg (shearHomIdx2R _ hk0_t211 zv hz x)) :=
    fun hg x => conjTorusIdx4_shear_Idx2R hk0_t211 zv hz hz0 E hg x
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · left
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := images_t120_three
    refine hasStrothType_of_conjTorus_Idx4 D hL (StrothTypeIndex.t120 3 le_rfl) E' fun j => ?_
    fin_cases j
    · exact ⟨(hE' _ _).trans (h1.trans i1.symm), (hE' _ _).trans (h2.trans i2.symm),
        (hE' _ _).trans (h3.trans i3.symm), (hE' _ _).trans (h4.trans i4.symm)⟩
    · exact ⟨(hE' _ _).trans (h5.trans i5.symm), (hE' _ _).trans (h6.trans i6.symm),
        (hE' _ _).trans (h7.trans i7.symm), (hE' _ _).trans (h8.trans i8.symm)⟩
    · exact ⟨(hE' _ _).trans (h9.trans i9.symm), (hE' _ _).trans (h10.trans i10.symm),
        (hE' _ _).trans (h11.trans i11.symm), (hE' _ _).trans (h12.trans i12.symm)⟩
  · right
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := images_t130_three
    refine hasStrothType_of_conjTorus_Idx4 D hL (StrothTypeIndex.t130 3 le_rfl) E' fun j => ?_
    fin_cases j
    · exact ⟨(hE' _ _).trans (h1.trans i1.symm), (hE' _ _).trans (h2.trans i2.symm),
        (hE' _ _).trans (h3.trans i3.symm), (hE' _ _).trans (h4.trans i4.symm)⟩
    · exact ⟨(hE' _ _).trans (h5.trans i5.symm), (hE' _ _).trans (h6.trans i6.symm),
        (hE' _ _).trans (h7.trans i7.symm), (hE' _ _).trans (h8.trans i8.symm)⟩
    · exact ⟨(hE' _ _).trans (h9.trans i9.symm), (hE' _ _).trans (h10.trans i10.symm),
        (hE' _ _).trans (h11.trans i11.symm), (hE' _ _).trans (h12.trans i12.symm)⟩

theorem hasStrothTypeOver_t120_or_t130_of_noInvolutionsCentralizing_t211 {m : ℕ} {hm : 2 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t211 m hm))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothTypeOver D C (StrothTypeIndex.t120 (m + 1) (by omega)) ∨
    HasStrothTypeOver D C (StrothTypeIndex.t130 (m + 1) (by omega)) := by
  have hm2 := eq_two_of_noInvolutionsCentralizing_t211_of_data D hBC hC hrel hL hH hcS hne
  subst hm2
  obtain ⟨d, hdC, -, hd2, E, hE0, hE1, hE2⟩ := exists_basis_t211_of_data D hBC hC hrel hL hH hcS hne
  have TV := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.uv_mem_L) D.uv_mem _ _
    D.uv_conj
  have TW := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.t_mem_L) D.t_mem _ _
    D.t_conj
  have TU := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.u_mem_L) D.u_mem _ _
    D.u_conj
  have TR := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.ρ_mem_L) D.ρ_mem _ _
    D.ρ_conj
  obtain ⟨zv, hz, hz0, h⟩ := classify_t211 _ _ _ _ (conjTorusIdx4_rels E D hL)
    (by rw [TV.1]; congr 1) (by rw [TV.2.1]; congr 1)
    (by rw [TV.2.2]; congr 1)
    (by rw [TW.1]; congr 1) (by rw [TW.2.1]; congr 1)
    (by rw [TW.2.2]; congr 1)
    (by rw [TU.1]; congr 1) (by rw [TU.2.1]; congr 1)
    (by rw [TU.2.2]; congr 1)
    (by rw [TR.1]; congr 1) (by rw [TR.2.1]; congr 1)
    (by rw [TR.2.2]; congr 1)
  let E' : Torus (Type120.k 3) ≃+ Additive C := (shearIdx2R _ hk0_t211 zv hz hz0).trans E
  have hE' : ∀ {g : S} (hg : g ∈ Subgroup.normalizer C) (x : Torus (Type120.k 3)),
      conjTorusIdx4 E' hg x =
        shearHomIdx2R _ hk0_t211 zv hz (conjTorusIdx4 E hg (shearHomIdx2R _ hk0_t211 zv hz x)) :=
    fun hg x => conjTorusIdx4_shear_Idx2R hk0_t211 zv hz hz0 E hg x
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · left
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := images_t120_three
    refine hasStrothTypeOver_of_conjTorus_Idx4 D hL (StrothTypeIndex.t120 3 le_rfl) E' fun j => ?_
    fin_cases j
    · exact ⟨(hE' _ _).trans (h1.trans i1.symm), (hE' _ _).trans (h2.trans i2.symm),
        (hE' _ _).trans (h3.trans i3.symm), (hE' _ _).trans (h4.trans i4.symm)⟩
    · exact ⟨(hE' _ _).trans (h5.trans i5.symm), (hE' _ _).trans (h6.trans i6.symm),
        (hE' _ _).trans (h7.trans i7.symm), (hE' _ _).trans (h8.trans i8.symm)⟩
    · exact ⟨(hE' _ _).trans (h9.trans i9.symm), (hE' _ _).trans (h10.trans i10.symm),
        (hE' _ _).trans (h11.trans i11.symm), (hE' _ _).trans (h12.trans i12.symm)⟩
  · right
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := images_t130_three
    refine hasStrothTypeOver_of_conjTorus_Idx4 D hL (StrothTypeIndex.t130 3 le_rfl) E' fun j => ?_
    fin_cases j
    · exact ⟨(hE' _ _).trans (h1.trans i1.symm), (hE' _ _).trans (h2.trans i2.symm),
        (hE' _ _).trans (h3.trans i3.symm), (hE' _ _).trans (h4.trans i4.symm)⟩
    · exact ⟨(hE' _ _).trans (h5.trans i5.symm), (hE' _ _).trans (h6.trans i6.symm),
        (hE' _ _).trans (h7.trans i7.symm), (hE' _ _).trans (h8.trans i8.symm)⟩
    · exact ⟨(hE' _ _).trans (h9.trans i9.symm), (hE' _ _).trans (h10.trans i10.symm),
        (hE' _ _).trans (h11.trans i11.symm), (hE' _ _).trans (h12.trans i12.symm)⟩

end CFSG.CGT.Stroth77
