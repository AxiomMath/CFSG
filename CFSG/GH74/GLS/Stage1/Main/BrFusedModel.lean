module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedPkg
public import CFSG.GH74.GLS.Stage1.Main.BrFusedSylow
public import CFSG.GH74.GLS.Stage1.Main.BrFusedPglGen
public import CFSG.GH74.GLS.Stage1.Main.BrFusedPglLin
public import CFSG.GH74.GLS.Stage1.Main.BrFusedPglUni

public section

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local
  CFSG.GH74.GLS.Stage1.Main

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

variable {F : Type} [Field F]

theorem normalizer_K2_of_C0 (M : ModelData F) (h2 : (2 : F) ≠ 0) {x : PG M} (hx : x ∈ C0 M) :
    x ∈ Subgroup.normalizer (K2 M : Set (PG M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact C0_conj_K2 M h2 hx hh
  · intro hh
    have := C0_conj_K2 M h2 ((C0 M).inv_mem hx) hh
    simpa [mul_assoc] using this

theorem dP_sq_mem_E {M : ModelData F} {i : Fˣ} (hii : i * i = -1) (hsc2 : sc2 i ∈ M.U2)
    (ha₀ : dgen i 1 ∈ M.U2) (hd : dRefl F ∈ M.U2) :
    dP M (dgen i 1) ha₀ * dP M (dgen i 1) ha₀ ∈ K1 M ⊔ K2 M := by
  have hinv : (sc2 (-i) : GL (Fin 2) F) = (sc2 i)⁻¹ := by
    rw [sc2_inv]
    congr 1
    have h1 : i * (-i) = 1 := by
      calc i * (-i) = -(i * i) := by rw [mul_neg]
        _ = -(-1) := by rw [hii]
        _ = 1 := by simp
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hsU : sc2 (-i) * dRefl F ∈ M.U2 := by
    rw [hinv]
    exact M.U2.mul_mem (M.U2.inv_mem hsc2) hd
  have hdet2 : (((-i : Fˣ) : F)) ^ 2 = -1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hii
    simp only [Units.val_mul, Units.val_neg, Units.val_one] at this
    calc (((-i : Fˣ) : F)) ^ 2 = (i : F) * i := by simp [sq]
      _ = -1 := this
  have hs : sc2 (-i) * dRefl F ∈ M.H2 := by
    refine (M.mem_H2 _).2 ⟨hsU, ?_⟩
    rw [Units.val_mul, Matrix.det_mul, det_sc2, det_dRefl, hdet2]
    norm_num
  rw [← sq, ← dP_dRefl_eq_sq hii ha₀ hd, mem_E_iff]
  refine ⟨⟨_, hs⟩, ⟨_, hs⟩, ?_⟩
  have hss := diagGL_mem_K4_of_H2 M ⟨_, hs⟩ ⟨_, hs⟩
  rw [iota_mul_eq_mkP_diag M ⟨_, hs⟩ ⟨_, hs⟩ hss, dP]
  apply (mkP_diag_eq_iff (diag_inv_mem_K4 M hd) hss).2
  refine ⟨-i, rfl, ?_⟩
  rw [dRefl_inv]


theorem fusedPkg_generic [Finite F] {M : ModelData F} (hG : GoodModel M) (hF : LUFacts M) {i : Fˣ}
    (hii : i * i = -1) (hsc2 : sc2 i ∈ M.U2) (ha₀ : dgen i 1 ∈ M.U2) (ha₀4 : dgen i 1 ^ 4 = 1)
    (hdet : ∀ s : Fˣ, sc4 s ∈ M.K4 →
      ((dgen i 1 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≠ (s : F) ^ 2)
    (hd : dRefl F ∈ M.U2)
    (hu : dP M (dRefl F) hd ∈ zpowers (dP M (dgen i 1) ha₀) ⊔ zpowers (tP M))
    {o : ℕ} (ho : Odd o) (hidx : ((K1 M ⊔ K2 M).subgroupOf (Cg M)).index = 4 * o)
    (hcs : ∀ s ∈ BSsub M, (∃ i : ℕ, s ^ 2 ^ i = 1) → s = 1 ∨ s = yP M) {q : ℕ} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hmod8 : ¬ ((q : ℤ) ≡ ε [ZMOD 8]))
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q)) {N : ℕ} (hNeq : (N : ℤ) = (q : ℤ) - ε)
    (hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ M.K4 → l ^ N = 1 ∧ m ^ N = 1)
    (hT : Nat.card ↥(torusT M) = N) (hpgl : FusedPGL (yP M) (K1 M) (dP M (dgen i 1) ha₀) q) :
    ∃ (S : Sylow 2 (PG M)) (t u n : PG M), FusedPkg (PG M) q ε (yP M) S (K1 M) (K2 M) t u n := by
  have h2 := hG.two_ne_zero
  obtain ⟨S, -, hnS, hsyl, hdec⟩ := exists_luSylow' hG hF ha₀ ha₀4 hdet hd hu ho hidx hcs
  refine ⟨S, tP M, dP M (dRefl F) hd, dP M (dgen i 1) ha₀, ?_⟩
  have hty : (MulAut.conj (tP M)) (yP M) = yP M := by
    rw [MulAut.conj_apply]
    have := Subgroup.mem_centralizer_singleton_iff.1 (tP_mem_Cg M)
    calc tP M * yP M * (tP M)⁻¹ = (tP M * yP M) * (tP M)⁻¹ := by group
      _ = (yP M * tP M) * (tP M)⁻¹ := by rw [← this]
      _ = yP M := by group
  have htn : (MulAut.conj (tP M)) (dP M (dgen i 1) ha₀) = (dP M (dgen i 1) ha₀)⁻¹ := by
    rw [MulAut.conj_apply]
    exact tP_conj_dP M ha₀
  have hpgl₂ : FusedPGL (yP M) (K2 M) (dP M (dgen i 1) ha₀) q := by
    have h1 := (hpgl.map (MulAut.conj (tP M))).inv
    rw [hty, htn, tP_swap M, inv_inv] at h1
    exact h1
  exact ⟨luModelData_PG_of hG hε hmod8 hSL hd hsyl hNeq hN hT, hnS,
    normalizer_K1_of_C0 M h2 (dP_mem_C0 M ha₀), normalizer_K2_of_C0 M h2 (dP_mem_C0 M ha₀),
    dP_sq_mem_E hii hsc2 ha₀ hd, hdec, layer_map_eq M h2 hG.qs, hpgl, hpgl₂⟩


theorem fusedPkg_lin [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (hq8 : Nat.card F % 8 = 5) :
    ∃ (S : Sylow 2 (PG (ModelData.lin F))) (t u n : PG (ModelData.lin F)),
      FusedPkg (PG (ModelData.lin F)) (Nat.card F) 1 (yP _) S (K1 _) (K2 _) t u n := by
  have hG := goodModel_lin h2 h5
  have hF := luFacts_lin h2
  obtain ⟨i, hii⟩ := exists_i_of_card (F := F) (by omega)
  have hi4 : i ^ 4 = 1 := pow_four_of_sq hii
  have hd : dRefl F ∈ (ModelData.lin F).U2 := Subgroup.mem_top _
  have ha₀ : dgen i 1 ∈ (ModelData.lin F).U2 := Subgroup.mem_top _
  have hi : sc4 i ∈ (ModelData.lin F).K4 := ((ModelData.lin F).mem_K4 _).2
    ⟨Subgroup.mem_top _, by
      rw [det_sc4]
      have := congrArg (fun u : Fˣ => (u : F)) hi4
      simpa using this⟩
  have hZ4 := card_Zs_four h2 hii hi
  have hU : Nat.card ↥(ModelData.lin F).U2 =
      Nat.card ↥(ModelData.lin F).H2 * (Nat.card F - 1) := card_U2_lin
  have hidx := index_E_Cg_eq (ModelData.lin F) (card_Cg_eq_four hG hZ4 hU)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 8 * k + 5 := ⟨Nat.card F / 8, by omega⟩
  have hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ (ModelData.lin F).K4 →
      l ^ (Nat.card F - 1) = 1 ∧ m ^ (Nat.card F - 1) = 1 :=
    fun l m _ => ⟨pow_card_sub_one_lin l, pow_card_sub_one_lin m⟩
  exact fusedPkg_generic hG hF hii (Subgroup.mem_top _) ha₀ (dgen_pow_four hi4 (by simp))
    (det_dgen_ne_sq h2 hii) hd
    (by
      rw [dP_dRefl_eq_sq hii ha₀ hd]
      exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2))
    (o := 2 * k + 1) ⟨k, rfl⟩ (by rw [hidx]; omega)
    (hcs_gen _ (N := Nat.card F - 1) (by omega) (fun l m hlm => (hN l m hlm).1))
    (q := Nat.card F) (ε := 1) (Or.inl rfl)
    (by
      intro h
      unfold Int.ModEq at h
      omega)
    (hasSL2Model_H2_lin F) (N := Nat.card F - 1) (by omega) hN (card_torusT_lin F)
    (fusedPGL_of_surj4 hii (Subgroup.mem_top _) ha₀ (lin_psi4 h2 h5 hq8))


theorem fusedPkg_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq8 : p ^ f % 8 = 3) :
    ∃ (S : Sylow 2 (PG (ModelData.uni hF))) (t u n : PG (ModelData.uni hF)),
      FusedPkg (PG (ModelData.uni hF)) (p ^ f) (-1) (yP _) S (K1 _) (K2 _) t u n := by
  have hG := goodModel_uni hF hp2 h5
  have hFu := luFacts_uni hF hp2
  have hcardF : Nat.card F % 4 ≠ 3 := by
    rw [hF, Nat.pow_mod, show p ^ f % 4 = 3 by omega]
    norm_num
  obtain ⟨i, hii⟩ := exists_i_of_card hcardF
  have hi4 := pow_four_of_sq hii
  have hiq : i ^ (p ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, p ^ f + 1 = 4 * m := ⟨(p ^ f + 1) / 4, by omega⟩
    rw [hm, pow_mul, hi4, _root_.one_pow]
  have hd : dRefl F ∈ (ModelData.uni hF).U2 := dRefl_mem_uni
  have ha₀ : dgen i 1 ∈ (ModelData.uni hF).U2 := dgen_mem_uni hF hiq
  have hsc2 : sc2 i ∈ (ModelData.uni hF).U2 := (sc2_mem_uni_iff hF i).2 hiq
  have hi : sc4 i ∈ (ModelData.uni hF).K4 :=
    sc4_mem_of_sc2_mem hsc2 (by rw [hii]; simp)
  have hZ4 := card_Zs_four hG.two_ne_zero hii hi
  have hU := card_U2_uni hF hp2
  have hidx := index_E_Cg_eq (ModelData.uni hF) (card_Cg_eq_four hG hZ4 hU)
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 8 * k + 3 := ⟨p ^ f / 8, by omega⟩
  have hN := hN_uni hF
  exact fusedPkg_generic hG hFu hii hsc2 ha₀ (dgen_pow_four hi4 (by simp))
    (det_dgen_ne_sq hG.two_ne_zero hii) hd
    (by
      rw [dP_dRefl_eq_sq hii ha₀ hd]
      exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2))
    (o := 2 * k + 1) ⟨k, rfl⟩ (by rw [hidx]; omega)
    (hcs_gen _ (N := p ^ f + 1) (by omega) (fun l m hlm => (hN l m hlm).1))
    (q := p ^ f) (ε := -1) (Or.inr rfl)
    (by
      intro h
      unfold Int.ModEq at h
      omega)
    (hasSL2Model_H2_uni hF) (N := p ^ f + 1) (by push_cast; ring) hN (card_torusT_uni hF)
    (fusedPGL_of_surj4 hii hsc2 ha₀ (uni_psi4 hF hp2 hq8))


theorem fusedPkg_transfer {Gs : Type} [Group Gs] [Finite Gs] {F : Type} [Field F] [Finite F]
    {M : ModelData F} (e : Gs ≃* PG M) {S₀ : Sylow 2 (PG M)}
    (hS₀ : CenterIs (S₀ : Subgroup (PG M)) (yP M)) (h2 : (2 : F) ≠ 0) (S' : Sylow 2 Gs) (z' : Gs)
    (hz' : (Subgroup.center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = Subgroup.zpowers z')
    {q : ℕ} {ε : ℤ} {E₁ E₂ : Subgroup (PG M)} {t u n : PG M}
    (hdata : FusedPkg (PG M) q ε (yP M) S₀ E₁ E₂ t u n) :
    ∃ (E₁' E₂' : Subgroup Gs) (t' u' n' : Gs), FusedPkg Gs q ε z' S' E₁' E₂' t' u' n' := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_sylow e S₀ S'
  have hz'c : CenterIs (S' : Subgroup Gs) z' := (centerIs_iff _ _).1 hz'
  have hΦz : Φ z' = yP M := equiv_center_eq Φ (orderOf_yP M h2) hΦ hz'c hS₀
  have hS : (S₀ : Subgroup (PG M)) = (S' : Subgroup Gs).map Φ.toMonoidHom := hΦ.symm
  have key := FusedPkg.map Φ.symm (S := S₀) (S' := S') (by
    rw [hS, CFSG.GH74.GLS.Stage2.Final.ModelLUT.map_symm_map]) hdata
  rw [show Φ.symm (yP M) = z' by rw [← hΦz]; simp] at key
  exact ⟨_, _, _, _, _, key⟩

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage1.Main

open CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.GLS.Stage2.Final CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup

theorem fusedModelLeaf : FusedModelLeaf := by
  intro Gs _ _ p f hp hp2 hq S' z' hz'
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  constructor
  · rintro ⟨h8, hL⟩
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    have h5 : 5 ≤ Nat.card F := by rw [hF]; exact hq
    obtain ⟨S₀, t, u, n, hd⟩ := fusedPkg_lin h2 h5 (by rw [hF]; exact h8)
    rw [hF] at hd
    exact fusedPkg_transfer (show Gs ≃* PG (ModelData.lin F) from e)
      ((centerIs_iff _ _).1 hd.data.syl.z_cen) h2 S' z' hz' hd
  · rintro ⟨h8, hU⟩
    obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    obtain ⟨S₀, t, u, n, hd⟩ := fusedPkg_uni hF hp2 hq h8
    exact fusedPkg_transfer (show Gs ≃* PG (ModelData.uni hF) from e)
      ((centerIs_iff _ _).1 hd.data.syl.z_cen) h2 S' z' hz' hd

end CFSG.GH74.GLS.Stage1.Main
