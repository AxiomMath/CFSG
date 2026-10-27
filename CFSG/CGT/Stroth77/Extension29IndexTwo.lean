module

public import CFSG.CGT.Stroth77.Extension29Classify

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem rho_gens_t111 (t : ℕ) :
    (StrothTypeIndex.t111 t).action.φρ (gen (StrothTypeIndex.t111 t).k 0) =
        gen (StrothTypeIndex.t111 t).k 0 ∧
    (StrothTypeIndex.t111 t).action.φρ (gen (StrothTypeIndex.t111 t).k 1) =
        gen (StrothTypeIndex.t111 t).k 2 ∧
    (StrothTypeIndex.t111 t).action.φρ (gen (StrothTypeIndex.t111 t).k 2) =
      (-2 : ℤ) • gen (StrothTypeIndex.t111 t).k 0 +
        (-1 : ℤ) • gen (StrothTypeIndex.t111 t).k 1 +
        (-1 : ℤ) • gen (StrothTypeIndex.t111 t).k 2 := by
  have hc := Type111.rho_c t
  have ha := Type111.rho_a t
  have hb := Type111.rho_b t
  simp only [Torus.c, Torus.a, Torus.b] at hc ha hb
  refine ⟨?_, ?_, ?_⟩
  · change (Type111.action t).φρ (gen (Type111.k t) 0) = gen (Type111.k t) 0
    rw [hc]
    module
  · change (Type111.action t).φρ (gen (Type111.k t) 1) = gen (Type111.k t) 2
    rw [ha]
    module
  · exact hb

theorem hk_t111 (t : ℕ) : ∀ i, 1 ≤ (StrothTypeIndex.t111 t).k i := by
  intro i
  fin_cases i <;> simp [StrothTypeIndex.k, Type111.k]

theorem exists_basis_t111_of_data {t : ℕ} (D : StrothTypeData B (StrothTypeIndex.t111 t))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    ∃ d : S, ∃ hdC : d ∈ C, d ∉ B ∧ d * d = (D.c : S) ∧
      ∃ E : Torus ![t + 3, t + 3, t + 3] ≃+ Additive C,
        E (gen _ 0) = Additive.ofMul ⟨d, hdC⟩ ∧
        E (gen _ 1) = Additive.ofMul ⟨D.a, hBC D.a.2⟩ ∧
        E (gen _ 2) = Additive.ofMul ⟨D.b, hBC D.b.2⟩ := by
  obtain ⟨hρ0, hρ1, hρ2⟩ := rho_gens_t111 t
  obtain ⟨d, hdC, hdB, hd2⟩ := exists_sq_eq_c_Idx2R D (-2) (hk_t111 t) hρ0 hρ1 hρ2
    hBC hC hrel (hL D.ρ_mem_L) hH hcS hne
  obtain ⟨E, hE0, hE1, hE2⟩ := exists_torusEquiv_Idx2R D (k' := ![t + 3, t + 3, t + 3])
    rfl rfl rfl hBC hC hrel hdC hdB hd2
  exact ⟨d, hdC, hdB, hd2, E, hE0, hE1, hE2⟩

theorem eq_zero_of_noInvolutionsCentralizing_t111_of_data {t : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t111 t))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) : t = 0 := by
  obtain ⟨d, hdC, -, hd2, E, hE0, hE1, hE2⟩ := exists_basis_t111_of_data D hBC hC hrel hL hH hcS hne
  have TU := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.u_mem_L) D.u_mem _ _
    D.u_conj
  have hUU := DFunLike.congr_fun (conjTorusIdx4_rels E D hL).u_sq
    (gen (![t + 3, t + 3, t + 3] : Fin 3 → ℕ) 0)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hUU
  have hM : ∀ i j, (StrothTypeIndex.t111 t).action.u i j = Type111.uM t i j := fun _ _ => rfl
  have h2 := eq_two_of_u_Idx2R (k' := ![t + 3, t + 3, t + 3]) (m := t + 2) (n := t + 3) rfl rfl
    rfl (by omega) (by omega) _ hUU 0 0 ?_ ?_ ?_
  · omega
  · rw [TU.1]
    congr 1
    funext i
    fin_cases i <;> simp [hM, Type111.uM, uMat, ofCols_apply, pow_succ]
    ring
  · rw [TU.2.1]
    congr 1
  · rw [TU.2.2]
    congr 1
    funext i
    fin_cases i <;> simp [hM, Type111.uM, uMat, ofCols_apply]

theorem images_t321 :
    (StrothTypeIndex.t321).action.φuv (gen (StrothTypeIndex.t321).k 0) =
        Torus.ofInt (Type321.k) ![-3, 1, -1] ∧
    (StrothTypeIndex.t321).action.φt (gen (StrothTypeIndex.t321).k 0) =
        Torus.ofInt (Type321.k) ![1, 1, 2] ∧
    (StrothTypeIndex.t321).action.φu (gen (StrothTypeIndex.t321).k 0) =
        Torus.ofInt (Type321.k) ![-1, 0, 0] ∧
    (StrothTypeIndex.t321).action.φρ (gen (StrothTypeIndex.t321).k 0) =
        Torus.ofInt (Type321.k) ![1, 0, 0] ∧
    (StrothTypeIndex.t321).action.φuv (gen (StrothTypeIndex.t321).k 1) =
        Torus.ofInt (Type321.k) ![4, 1, 6] ∧
    (StrothTypeIndex.t321).action.φt (gen (StrothTypeIndex.t321).k 1) =
        Torus.ofInt (Type321.k) ![0, 3, 0] ∧
    (StrothTypeIndex.t321).action.φu (gen (StrothTypeIndex.t321).k 1) =
        Torus.ofInt (Type321.k) ![0, 0, 1] ∧
    (StrothTypeIndex.t321).action.φρ (gen (StrothTypeIndex.t321).k 1) =
        Torus.ofInt (Type321.k) ![0, 0, 1] ∧
    (StrothTypeIndex.t321).action.φuv (gen (StrothTypeIndex.t321).k 2) =
        Torus.ofInt (Type321.k) ![84, 22, -7] ∧
    (StrothTypeIndex.t321).action.φt (gen (StrothTypeIndex.t321).k 2) =
        Torus.ofInt (Type321.k) ![28, -6, -5] ∧
    (StrothTypeIndex.t321).action.φu (gen (StrothTypeIndex.t321).k 2) =
        Torus.ofInt (Type321.k) ![0, 1, 0] ∧
    (StrothTypeIndex.t321).action.φρ (gen (StrothTypeIndex.t321).k 2) =
        Torus.ofInt (Type321.k) ![4, -1, -1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (matAct_gen_ofInt_Idx2R _ _ _).trans (by congr 1 <;> decide)

theorem images_t331 :
    (StrothTypeIndex.t331).action.φuv (gen (StrothTypeIndex.t331).k 0) =
        Torus.ofInt (Type321.k) ![-3, 5, -1] ∧
    (StrothTypeIndex.t331).action.φt (gen (StrothTypeIndex.t331).k 0) =
        Torus.ofInt (Type321.k) ![1, 1, -2] ∧
    (StrothTypeIndex.t331).action.φu (gen (StrothTypeIndex.t331).k 0) =
        Torus.ofInt (Type321.k) ![3, 0, 0] ∧
    (StrothTypeIndex.t331).action.φρ (gen (StrothTypeIndex.t331).k 0) =
        Torus.ofInt (Type321.k) ![1, 0, 0] ∧
    (StrothTypeIndex.t331).action.φuv (gen (StrothTypeIndex.t331).k 1) =
        Torus.ofInt (Type321.k) ![4, 1, 6] ∧
    (StrothTypeIndex.t331).action.φt (gen (StrothTypeIndex.t331).k 1) =
        Torus.ofInt (Type321.k) ![0, 3, 0] ∧
    (StrothTypeIndex.t331).action.φu (gen (StrothTypeIndex.t331).k 1) =
        Torus.ofInt (Type321.k) ![0, 0, 1] ∧
    (StrothTypeIndex.t331).action.φρ (gen (StrothTypeIndex.t331).k 1) =
        Torus.ofInt (Type321.k) ![0, 0, 1] ∧
    (StrothTypeIndex.t331).action.φuv (gen (StrothTypeIndex.t331).k 2) =
        Torus.ofInt (Type321.k) ![20, 38, 9] ∧
    (StrothTypeIndex.t331).action.φt (gen (StrothTypeIndex.t331).k 2) =
        Torus.ofInt (Type321.k) ![28, -6, -5] ∧
    (StrothTypeIndex.t331).action.φu (gen (StrothTypeIndex.t331).k 2) =
        Torus.ofInt (Type321.k) ![0, 1, 0] ∧
    (StrothTypeIndex.t331).action.φρ (gen (StrothTypeIndex.t331).k 2) =
        Torus.ofInt (Type321.k) ![4, -1, -1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (matAct_gen_ofInt_Idx2R _ _ _).trans (by congr 1 <;> decide)

theorem hasStrothTypeOver_t321_or_t331_of_noInvolutionsCentralizing_t111 {t : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t111 t))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B) :
    HasStrothTypeOver D C StrothTypeIndex.t321 ∨ HasStrothTypeOver D C StrothTypeIndex.t331 := by
  have ht0 := eq_zero_of_noInvolutionsCentralizing_t111_of_data D hBC hC hrel hL hH hcS hne
  subst ht0
  obtain ⟨d, hdC, -, hd2, E₀, hE₀0, hE₀1, hE₀2⟩ :=
    exists_basis_t111_of_data D hBC hC hrel hL hH hcS hne
  let E : Torus Type321.k ≃+ Additive C := E₀
  have hE0 : E (gen Type321.k 0) = Additive.ofMul ⟨d, hdC⟩ := hE₀0
  have hE1 : E (gen Type321.k 1) = Additive.ofMul ⟨D.a, hBC D.a.2⟩ := hE₀1
  have hE2 : E (gen Type321.k 2) = Additive.ofMul ⟨D.b, hBC D.b.2⟩ := hE₀2
  have TV := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.uv_mem_L) D.uv_mem _ _
    D.uv_conj
  have TW := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.t_mem_L) D.t_mem _ _
    D.t_conj
  have TU := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.u_mem_L) D.u_mem _ _
    D.u_conj
  have TR := conjTorus_gen_Idx2R D hBC hdC E hE0 hE1 hE2 hd2 (hL D.ρ_mem_L) D.ρ_mem _ _
    D.ρ_conj
  obtain ⟨zv, hz, hz0, h⟩ := classify_t111 _ _ _ _ (conjTorusIdx4_rels E D hL)
    (by rw [TV.1]; congr 1) (by rw [TV.2.1]; congr 1)
    (by rw [TV.2.2]; congr 1)
    (by rw [TW.1]; congr 1) (by rw [TW.2.1]; congr 1)
    (by rw [TW.2.2]; congr 1)
    (by rw [TU.1]; congr 1) (by rw [TU.2.1]; congr 1)
    (by rw [TU.2.2]; congr 1)
    (by rw [TR.1]; congr 1) (by rw [TR.2.1]; congr 1)
    (by rw [TR.2.2]; congr 1)
  let E' : Torus Type321.k ≃+ Additive C := (shearIdx2R _ hk0_t111 zv hz hz0).trans E
  have hE' : ∀ {g : S} (hg : g ∈ Subgroup.normalizer C) (x : Torus Type321.k),
      conjTorusIdx4 E' hg x =
        shearHomIdx2R _ hk0_t111 zv hz (conjTorusIdx4 E hg (shearHomIdx2R _ hk0_t111 zv hz x)) :=
    fun hg x => conjTorusIdx4_shear_Idx2R hk0_t111 zv hz hz0 E hg x
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · left
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := images_t321
    refine hasStrothTypeOver_of_conjTorus_Idx4 D hL StrothTypeIndex.t321 E' fun j => ?_
    fin_cases j
    · exact ⟨(hE' _ _).trans (h1.trans i1.symm), (hE' _ _).trans (h2.trans i2.symm),
        (hE' _ _).trans (h3.trans i3.symm), (hE' _ _).trans (h4.trans i4.symm)⟩
    · exact ⟨(hE' _ _).trans (h5.trans i5.symm), (hE' _ _).trans (h6.trans i6.symm),
        (hE' _ _).trans (h7.trans i7.symm), (hE' _ _).trans (h8.trans i8.symm)⟩
    · exact ⟨(hE' _ _).trans (h9.trans i9.symm), (hE' _ _).trans (h10.trans i10.symm),
        (hE' _ _).trans (h11.trans i11.symm), (hE' _ _).trans (h12.trans i12.symm)⟩
  · right
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12⟩ := images_t331
    refine hasStrothTypeOver_of_conjTorus_Idx4 D hL StrothTypeIndex.t331 E' fun j => ?_
    fin_cases j
    · exact ⟨(hE' _ _).trans (h1.trans i1.symm), (hE' _ _).trans (h2.trans i2.symm),
        (hE' _ _).trans (h3.trans i3.symm), (hE' _ _).trans (h4.trans i4.symm)⟩
    · exact ⟨(hE' _ _).trans (h5.trans i5.symm), (hE' _ _).trans (h6.trans i6.symm),
        (hE' _ _).trans (h7.trans i7.symm), (hE' _ _).trans (h8.trans i8.symm)⟩
    · exact ⟨(hE' _ _).trans (h9.trans i9.symm), (hE' _ _).trans (h10.trans i10.symm),
        (hE' _ _).trans (h11.trans i11.symm), (hE' _ _).trans (h12.trans i12.symm)⟩

end CFSG.CGT.Stroth77
