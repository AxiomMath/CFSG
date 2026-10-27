module

public import CFSG.GH74.GLS.LU.Local.FiveStdRed
public import CFSG.GH74.GLS.LU.Local.FiveStdMat8
public import CFSG.GH74.GLS.LU.Local.FiveCfg2
public import CFSG.GH74.GLS.LU.Local.FiveStdRepN
public import CFSG.GH74.GLS.LU.Local.FiveStdRepX1d
public import CFSG.GH74.GLS.LU.Local.FiveStdDiag
public import CFSG.GH74.GLS.LU.Local.FiveStdRepA3
public import CFSG.GH74.GLS.Stage2.Final.ModelComps
public import CFSG.GH74.GLS.Stage2.Final.ModelLUTransport

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local
  CFSG.GH74.GLS.Stage2.Final.ModelBlock

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.FiveStd.Mat CFSG.GH74.L5U5
  CFSG.GH74.GLS.Stage2.Final

variable {Gs : Type} [Group Gs] [Finite Gs] {F : Type} [Field F] [Finite F] [CharP F 5]

theorem exists_psi (hF5 : Nat.card F = 5) (hb : baseCheck = true) (e : Gs ≃* PG (ModelData.lin F))
    (S' : Sylow 2 Gs) (z' : Gs) (hz'ord : orderOf z' = 2) (hz'c : CenterIs (S' : Subgroup Gs) z') :
    ∃ (S₀ : Sylow 2 (PG (ModelData.lin F))) (Ψ : Gs ≃* PG (ModelData.lin F)),
      ((S₀ : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) = S (ιF F) S0 ∧
      CenterIs (S₀ : Subgroup (PG (ModelData.lin F))) (yP (ModelData.lin F)) ∧
      K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F) ⊔ (S₀ : Subgroup (PG (ModelData.lin F))) =
        Cz (yP (ModelData.lin F)) ∧
      Ψ z' = yP (ModelData.lin F) ∧ (S' : Subgroup Gs).map Ψ.toMonoidHom = (S₀ : Subgroup (PG (ModelData.lin F))) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_F
  let st := fiveStdSetting (F := F) hF5
  have hz : st.z = yP (ModelData.lin F) := ιF_zE
  have hodd : Odd (Cz st.z).index := by
    rw [hz]
    show Odd (Subgroup.centralizer ({yP (ModelData.lin F)} : Set (PG (ModelData.lin F)))).index
    rw [index_C]
    exact odd_index_Nsub _ h2 (ModelOrd.odd_index_lin F h2)
  obtain ⟨S₀, hset, hcen, hsup⟩ := st.exists_sylow_std hb hodd
  rw [hz] at hcen hsup
  obtain ⟨Ψ, hΨz, hΨS⟩ := exists_equiv_sylow e S₀ (yP (ModelData.lin F)) (orderOf_yP _ h2) hcen S' z'
    hz'ord hz'c
  exact ⟨S₀, Ψ, hset, hcen, hsup, hΨz, hΨS⟩

omit [Finite Gs] [CharP F 5] in
theorem hasSL2Model_five (hF5 : Nat.card F = 5) :
    HasSL2Model ↥(ModelData.lin F).H2 (fun r => r = 5) := by
  have h := hasSL2Model_H2_lin F
  rw [hF5] at h
  exact h

theorem comps_cases (hF5 : Nat.card F = 5) (hO : pPrimeCoreOf 2 (Cz (yP (ModelData.lin F))) = ⊥)
    {A B : Subgroup (PG (ModelData.lin F))} (h : LUComps (PG (ModelData.lin F)) 5 (yP (ModelData.lin F)) A B) :
    (A = K1 (ModelData.lin F) ∧ B = K2 (ModelData.lin F)) ∨
      (A = K2 (ModelData.lin F) ∧ B = K1 (ModelData.lin F)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_F
  have h5 : 5 ≤ Nat.card F := by rw [hF5]
  have hG := goodModel_lin h2 h5
  have hL0 := luComps_PG hG 5 (hasSL2Model_five hF5)
  have hK1 := isPCompIn_two_of_isCompIn hO (isCompIn_K1 hG)
  have hK2 := isPCompIn_two_of_isCompIn hO (isCompIn_K2 hG)
  have h1 := h.only _ hK1
  have h2' := h.only _ hK2
  have hne := hL0.ne
  rcases h1 with h1 | h1 <;> rcases h2' with h2' | h2'
  · exact absurd (h1.trans h2'.symm) hne
  · exact Or.inl ⟨h1.symm, h2'.symm⟩
  · exact Or.inr ⟨h2'.symm, h1.symm⟩
  · exact absurd (h1.trans h2'.symm) hne

omit [Finite F] [CharP F 5] in
theorem oddCore_card_one (hL : LieModel Gs .PSL 4 5 1) (S' : Sylow 2 Gs) (z' : Gs)
    (hz'ord : orderOf z' = 2)
    (hz'c : (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z') :
    Nat.card ↥(pPrimeCore 2 ↥(centralizer ({z'} : Set Gs))) = 1 := by
  have hcl : IsClassicalModel Gs 5 1 :=
    ⟨Nat.prime_five, by norm_num, by norm_num, Or.inr (Or.inl ⟨by norm_num, hL⟩)⟩
  have h := (modelOddCore Gs 5 1 S' z' hcl hz'ord hz'c).1 (by norm_num) hL
  rw [h]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact padicValNat.prime_pow 2
  norm_num [h4]

theorem card_K1_eq_K2 (F : Type) [Field F] [Finite F] :
    Nat.card ↥(K1 (ModelData.lin F)) = Nat.card ↥(K2 (ModelData.lin F)) := by
  have h1 := Nat.card_congr (MonoidHom.ofInjective (iota1_injective (ModelData.lin F))).toEquiv
  have h2 := Nat.card_congr (MonoidHom.ofInjective (iota2_injective (ModelData.lin F))).toEquiv
  exact h1.symm.trans h2

theorem exists_swap (hF5 : Nat.card F = 5) (hc : fiveStdCheck = true) (S₀ : Sylow 2 (PG (ModelData.lin F)))
    (hset : ((S₀ : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) = S (ιF F) S0) :
    ∃ τ ∈ (S₀ : Subgroup (PG (ModelData.lin F))), τ * τ = 1 ∧
      cjL τ (K1 (ModelData.lin F)) = K2 (ModelData.lin F) := by
  obtain ⟨hb, hs, hd, hcov, hreps⟩ := fiveStdCheck_spec hc
  obtain ⟨-, hpc, -⟩ := coverCheck_spec hcov
  obtain ⟨-, hV1, hV2, hV0, -⟩ := baseCheck_spec hb
  let st := fiveStdSetting (F := F) hF5
  obtain ⟨r₀, hr₀⟩ := List.exists_mem_of_ne_nil reps (by simp [reps])
  have hp := hpc r₀ hr₀
  unfold pairCond at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨⟨hts, hun⟩, hot⟩, hou⟩, hu⟩, hcm⟩ := hp
  have hts' : r₀.1 ∈ S0.filter swapsK := List.contains_iff_mem.1 hts
  obtain ⟨hmem, hsw⟩ := List.mem_filter.1 hts'
  have hv : validE r₀.1 = true := hV0 _ hmem
  have hordt : orderOf (ιF F r₀.1) = 2 := st.model.orderOf_of_ordE hv hot (by norm_num)
  have hsq : ιF F r₀.1 * ιF F r₀.1 = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one (ιF F r₀.1)
    rwa [hordt] at this
  refine ⟨ιF F r₀.1, ?_, hsq, ?_⟩
  · rw [← SetLike.mem_coe, hset]
    exact mem_S.2 ⟨_, hmem, rfl⟩
  · have hle : cjL (ιF F r₀.1) (K1 (ModelData.lin F)) ≤ K2 (ModelData.lin F) := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' : k ∈ S (ιF F) K1l := by rw [S_K1l hF5]; exact hk
      obtain ⟨x, hx, rfl⟩ := mem_S.1 hk'
      have hxv : validE x = true := hV1 x hx
      unfold swapsK at hsw
      rw [List.all_eq_true] at hsw
      have h1 := hsw x hx
      have h2 := (st.model.inL_iff hV2 (st.model.valid_conjE hv hxv)).1 h1
      rw [st.model.map_conjE hv hxv] at h2
      have h3 : st.ι r₀.1 * st.ι x * (st.ι r₀.1)⁻¹ ∈
          ((K2 (ModelData.lin F) : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) := by
        rw [← S_K2l hF5]
        exact h2
      exact h3
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (ιF F r₀.1)).injective]
    exact (card_K1_eq_K2 F).ge

omit [Finite Gs] [Finite F] [CharP F 5] in
theorem map_trans_conj {G : Type} [Group G] (Ψ : Gs ≃* G) (τ : G) (K : Subgroup Gs) :
    K.map (Ψ.trans (MulAut.conj τ)).toMonoidHom = cjL τ (K.map Ψ.toMonoidHom) := by
  unfold cjL
  rw [Subgroup.map_map]
  rfl

theorem exists_psi_comps (hF5 : Nat.card F = 5) (hc : fiveStdCheck = true) (hL : LieModel Gs .PSL 4 5 1)
    (e : Gs ≃* PG (ModelData.lin F)) (S' : Sylow 2 Gs) (z' : Gs) (K₁' K₂' : Subgroup Gs)
    (hcomps : LUComps Gs 5 z' K₁' K₂') (hz'ord : orderOf z' = 2) (hz'c : CenterIs (S' : Subgroup Gs) z') :
    ∃ (S₀ : Sylow 2 (PG (ModelData.lin F))) (Ψ : Gs ≃* PG (ModelData.lin F)),
      ((S₀ : Subgroup (PG (ModelData.lin F))) : Set (PG (ModelData.lin F))) = S (ιF F) S0 ∧
      CenterIs (S₀ : Subgroup (PG (ModelData.lin F))) (yP (ModelData.lin F)) ∧
      K1 (ModelData.lin F) ⊔ K2 (ModelData.lin F) ⊔ (S₀ : Subgroup (PG (ModelData.lin F))) =
        Cz (yP (ModelData.lin F)) ∧
      Ψ z' = yP (ModelData.lin F) ∧
      (S' : Subgroup Gs).map Ψ.toMonoidHom = (S₀ : Subgroup (PG (ModelData.lin F))) ∧
      K₁'.map Ψ.toMonoidHom = K1 (ModelData.lin F) ∧ K₂'.map Ψ.toMonoidHom = K2 (ModelData.lin F) := by
  obtain ⟨hb, -⟩ := fiveStdCheck_spec hc
  obtain ⟨S₀, Ψ, hset, hcen, hsup, hΨz, hΨS⟩ := exists_psi hF5 hb e S' z' hz'ord hz'c
  have hcomps' := CFSG.GH74.GLS.Stage2.Final.ModelLUT.luComps_map Ψ hcomps
  rw [hΨz] at hcomps'
  have hO : pPrimeCoreOf 2 (Cz (yP (ModelData.lin F))) = ⊥ := by
    have h1 := oddCore_card_one hL S' z' hz'ord ((centerIs_iff _ _).2 hz'c)
    have h2 := card_pPrimeCore_centralizer_of_equiv Ψ z'
    rw [hΨz, h1] at h2
    have h3 : pPrimeCore 2 ↥(centralizer ({yP (ModelData.lin F)} : Set (PG (ModelData.lin F)))) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ h2.symm
    show (pPrimeCore 2 ↥(Cz (yP (ModelData.lin F)))).map (Cz (yP (ModelData.lin F))).subtype = ⊥
    rw [h3, Subgroup.map_bot]
  rcases comps_cases hF5 hO hcomps' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨S₀, Ψ, hset, hcen, hsup, hΨz, hΨS, h1, h2⟩
  · obtain ⟨τ, hτS, hτ2, hτK⟩ := exists_swap hF5 hc S₀ hset
    have hτz : τ * yP (ModelData.lin F) = yP (ModelData.lin F) * τ :=
      ((hcen _).2 (Subgroup.mem_zpowers _)).2 τ hτS
    have hKK : cjL τ (K2 (ModelData.lin F)) = K1 (ModelData.lin F) := by
      rw [← hτK, cjL_cjL, hτ2, cjL_one]
    refine ⟨S₀, Ψ.trans (MulAut.conj τ), hset, hcen, hsup, ?_, ?_, ?_, ?_⟩
    · show τ * Ψ z' * τ⁻¹ = _
      rw [hΨz, mul_inv_eq_iff_eq_mul]
      exact hτz
    · rw [map_trans_conj, hΨS]
      exact cjL_eq_of_mem_normalizer (Subgroup.le_normalizer hτS)
    · rw [map_trans_conj, h1, hKK]
    · rw [map_trans_conj, h2, hτK]

namespace FiveStdSetting

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

theorem facts_of_rep (hc : fiveStdCheck = true) {tE uE : E} (hr : (tE, uE) ∈ reps) (S' : Sylow 2 G) :
    FiveModelFacts st.z S' st.K₁ st.K₂ (st.ι tE) (st.ι uE) := by
  obtain ⟨hb, hs, hd, hcov, hreps⟩ := fiveStdCheck_spec hc
  obtain ⟨-, hpc, -⟩ := coverCheck_spec hcov
  have hp := hpc _ hr
  have hrep := hreps _ hr
  obtain ⟨hP2, hPc, htex, huniq, hfacts, hw, ht⟩ := st.rep_A hb hp hrep
  obtain ⟨hnoinv, hsyl⟩ := st.rep_N hb hs hp hrep
  exact ⟨hP2, hPc, htex, huniq, hfacts, hw, ht, st.rep_X1 hb hs hp hrep, st.diag_sound hb hd, hnoinv, hsyl⟩

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five
